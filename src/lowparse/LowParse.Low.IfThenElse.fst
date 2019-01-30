module LowParse.Low.IfThenElse
include LowParse.Spec.IfThenElse
include LowParse.Low.Combinators

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let valid_ifthenelse_intro
  (p: parse_ifthenelse_param)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t
  )))
  (ensures (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t /\
    valid_content_pos
      (parse_ifthenelse p) h sl pos
      (p.parse_ifthenelse_synth
        t
        (contents (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
      )
      (get_valid_pos (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
  )))
= valid_facts (parse_ifthenelse p) h sl pos;
  valid_facts p.parse_ifthenelse_tag_parser h sl pos;
  let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
  let t = contents p.parse_ifthenelse_tag_parser h sl pos in
  let b = p.parse_ifthenelse_tag_cond t in
  valid_facts (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t;
  parse_ifthenelse_eq p (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)))

let valid_ifthenelse_elim
  (p: parse_ifthenelse_param)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (valid (parse_ifthenelse p) h sl pos))
  (ensures (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t /\
    valid_content_pos
      (parse_ifthenelse p) h sl pos
      (p.parse_ifthenelse_synth
        t
        (contents (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
      )
      (get_valid_pos (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
  )))
= valid_facts (parse_ifthenelse p) h sl pos;
  parse_ifthenelse_eq p (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)));
  valid_facts p.parse_ifthenelse_tag_parser h sl pos;
  let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
  let t = contents p.parse_ifthenelse_tag_parser h sl pos in
  let b = p.parse_ifthenelse_tag_cond t in
  valid_facts (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t

inline_for_extraction
type test_ifthenelse_tag
  (p: parse_ifthenelse_param)
= (input: slice) ->
  (pos: U32.t) ->
  HST.Stack bool
  (requires (fun h -> valid p.parse_ifthenelse_tag_parser h input pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == p.parse_ifthenelse_tag_cond (contents p.parse_ifthenelse_tag_parser h input pos)
  ))

inline_for_extraction
let validate_ifthenelse
  (p: parse_ifthenelse_param)
  (vt: validator p.parse_ifthenelse_tag_parser)
  (test: test_ifthenelse_tag p)
  (vp: (b: bool) -> Tot (validator (dsnd (p.parse_ifthenelse_payload_parser b))))
: Tot (validator (parse_ifthenelse p))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.move_requires (valid_ifthenelse_intro p h input) pos;
    Classical.move_requires (valid_ifthenelse_elim p h input) pos
  in
  let pos_after_t = vt input pos in
  if validator_max_length `U32.lt` pos_after_t
  then pos_after_t
  else
    let b = test input pos in
    if b (* eta-expansion here *)
    then vp true input pos_after_t
    else vp false input pos_after_t

inline_for_extraction
let jump_ifthenelse
  (p: parse_ifthenelse_param)
  (vt: jumper p.parse_ifthenelse_tag_parser)
  (test: test_ifthenelse_tag p)
  (vp: (b: bool) -> Tot (jumper (dsnd (p.parse_ifthenelse_payload_parser b))))
: Tot (jumper (parse_ifthenelse p))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.move_requires (valid_ifthenelse_elim p h input) pos
  in
  let pos_after_t = vt input pos in
  let b = test input pos in
  if b (* eta-expansion here *)
  then vp true input pos_after_t
  else vp false input pos_after_t

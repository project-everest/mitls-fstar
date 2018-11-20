module LowParse.Low.Sum
include LowParse.Low.Enum
include LowParse.Spec.Sum

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

inline_for_extraction
let validate_sum_aux_payload_t
  [| validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot Type
= (input: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h input /\ U32.v pos <= U32.v input.len /\ U32.v input.len <= U32.v validator_max_length))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    match k with
    | Unknown _ -> U32.v res > U32.v validator_max_length
    | Known k' ->
      if U32.v res <= U32.v validator_max_length
      then
        valid_pos (dsnd (pc k')) h input pos res
      else
        (~ (valid (dsnd (pc k')) h input pos))
  )))

let validate_sum_aux_payload_eq
  [| cls: validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (validate_sum_aux_payload_t t pc k -> validate_sum_aux_payload_t #cls t pc k -> GTot Type0)
= fun _ _ -> True

inline_for_extraction
let validate_sum_aux_payload_if'
  [| validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (cond: bool)
  (ift: ((cond_true cond) -> Tot (validate_sum_aux_payload_t t pc k)))
  (iff: ((cond_false cond) -> Tot (validate_sum_aux_payload_t t pc k)))
: Tot (validate_sum_aux_payload_t t pc k)
= fun input pos ->
  if cond
  then begin
    (ift () <: validate_sum_aux_payload_t t pc k) input pos
  end else
    (iff () <: validate_sum_aux_payload_t t pc k) input pos

inline_for_extraction
let validate_sum_aux_payload_if
  [| validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (if_combinator _ (validate_sum_aux_payload_eq t pc k))
= validate_sum_aux_payload_if' t pc k

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --initial_ifuel 8 --max_ifuel 8 --initial_fuel 2 --max_fuel 2"
// --query_stats  --smtencoding.elim_box true --smtencoding.l_arith_repr native --z3refresh"

inline_for_extraction
let validate_sum_aux
  [| validator_cls |]
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (v_payload: ((k: sum_repr_type t)) -> Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k)))
: Tot (validator (parse_sum t p pc))
= fun input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = parse_sum_eq'' t p pc (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos))) in
  [@inline_let]
  let _ = valid_facts (parse_sum t p pc) h input pos in
  [@inline_let]
  let _ = valid_facts p h input pos in
  let len_after_tag = v input pos in
  if validator_max_length `U32.lt` len_after_tag
  then len_after_tag
  else begin
    let h1 = HST.get () in
    let k' = p32 input pos in
    [@inline_let]
    let _ =
      match maybe_enum_key_of_repr (sum_enum t) k' with
      | Known k -> valid_facts (dsnd (pc k)) h input len_after_tag
      | _ -> ()
    in
    v_payload k' input len_after_tag
  end

#reset-options

inline_for_extraction
let validate_sum_aux_payload'
  [| cls: validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator #cls (dsnd (pc x)))))
  (k: maybe_enum_key (sum_enum t))
: Tot (validate_sum_aux_payload_t #cls t pc k)
= fun input pos ->
    match k with
    | Known k ->
      [@inline_let]
      let _ = synth_sum_case_injective t k in
      pc32 k input pos
      // validate_synth (pc32 k) (synth_sum_case t k) () input pos
    | _ -> validator_max_length `U32.add` 1ul

inline_for_extraction
let validate_sum_aux_payload
  [| validator_cls |]
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
  (k: sum_repr_type t)
: Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k))
= destr (validate_sum_aux_payload_eq t pc) (validate_sum_aux_payload_if t pc) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_sum_aux_payload' t pc pc32) k

inline_for_extraction
let validate_sum
  [| validator_cls |]
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
: Tot (validator (parse_sum t p pc))
= validate_sum_aux t v p32 pc (validate_sum_aux_payload t pc pc32 destr)

module HS = FStar.HyperStack

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --initial_ifuel 8 --max_ifuel 8 --initial_fuel 2 --max_fuel 2"

let valid_sum_intro
  (h: HS.mem)
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_enum_key p (sum_enum t)) h input pos /\ (
    let k = contents (parse_enum_key p (sum_enum t)) h input pos in
    valid (dsnd (pc k)) h input (get_valid_pos (parse_enum_key p (sum_enum t)) h input pos)
  )))
  (ensures (
    let k = contents (parse_enum_key p (sum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_enum_key p (sum_enum t)) h input pos in
    valid_content_pos
      (parse_sum t p pc) h input pos
      (synth_sum_case t k (contents (dsnd (pc k)) h input pos_payload))
      (get_valid_pos (dsnd (pc k)) h input pos_payload)
  ))
= valid_facts (parse_enum_key p (sum_enum t)) h input pos;
  let k = contents (parse_enum_key p (sum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_enum_key p (sum_enum t)) h input pos in
  valid_facts (dsnd (pc k)) h input pos_payload;
  valid_facts (parse_sum t p pc) h input pos;
  parse_sum_eq t p pc (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)))

#reset-options

(*
let clens_sum_payload
  (s: sum)
  (k: sum_key s)
: Tot (clens #(sum_type s) (fun (x: sum_type s) -> sum_tag_of_data s x == k) (sum_type_of_tag s k))
= {
  clens_get = (fun (x: sum_type s) -> synth_sum_case_recip s k x <: Ghost (sum_type_of_tag s k) (requires (sum_tag_of_data s x == k)) (ensures (fun _ -> True)));
}

let gaccessor_clens_sum_payload
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (gaccessor (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k))
= fun (input: bytes) ->
  if Seq.length input >= 
  

(*
inline_for_extraction
let validate32_dsum_type_of_tag
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (vf: (x: dsum_known_key s) -> Tot (validator32 (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (vg: validator32 g)
  (x: dsum_key s)
: Tot (validator32 (parse_dsum_type_of_tag s f g x))
= match x with
  | Known x -> (fun input len -> vf x input len)
  | Unknown _ -> (fun input len -> vg input len)

inline_for_extraction
let validate32_dsum_cases_t
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= validator32 (parse_dsum_cases s f g x)

inline_for_extraction
let validate32_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (vf: (x: dsum_known_key s) -> Tot (validator32 (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (vg: validator32 g)
  (x: dsum_key s)
: Tot (validate32_dsum_cases_t s f g x)
= [@inline_let]
  let _ = synth_dsum_case_injective s x in
  validate32_synth (validate32_dsum_type_of_tag s f vf g vg x) (synth_dsum_case s x) ()

let validate32_dsum_cases_eq
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (v1 v2 : validate32_dsum_cases_t s f g x)
: GTot Type0
= True

inline_for_extraction
let validate32_dsum_cases_if'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (cond: bool)
  (ift: (cond_true cond -> Tot (validate32_dsum_cases_t s f g x)))
  (iff: (cond_false cond -> Tot (validate32_dsum_cases_t s f g x)))
: Tot (validate32_dsum_cases_t s f g x)
= fun input len ->
  if cond
  then (ift () <: validate32_dsum_cases_t s f g x) input len
  else (iff () <: validate32_dsum_cases_t s f g x) input len

inline_for_extraction
let validate32_dsum_cases_if
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator _ (validate32_dsum_cases_eq s f g x))
= validate32_dsum_cases_if' s f g x

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --query_stats --initial_ifuel 1 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.l_arith_repr native --z3refresh"

inline_for_extraction
let validate32_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (v: validator32 p)
  (p32: parser32 p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (validator32 (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: validator32 g)
//  (v32: (x: dsum_repr_type t) -> Tot (validate32_dsum_cases_t t f g (maybe_enum_key_of_repr (dsum_enum t) x)))
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (validate32_dsum_cases_t t f g))
: Tot (validator32 (parse_dsum t p f g))
= fun input len ->
  let h = HST.get () in
  [@inline_let]
  let _ = parse_dsum_eq'' t p f g (B.as_seq h input) in
  let len_after_tag = v input len in
  if len_after_tag `I32.lt` 0l
  then len_after_tag
  else
    let tg = p32 input in
    let input_after_tag = B.offset input (Cast.int32_to_uint32 (len `I32.sub` len_after_tag)) in
//    v32 tg input_after_tag len_after_tag
    destr (validate32_dsum_cases_eq t f g) (validate32_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate32_dsum_cases t f f32 g g32) tg input_after_tag len_after_tag

#reset-options

module LowParse.SLow.Sum
include LowParse.Spec.Sum
include LowParse.SLow.Enum

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

let serializer32_sum_gen_precond
  (kt: parser_kind)
  (k: parser_kind)
: GTot Type0
= kt.parser_kind_subkind == Some ParserStrong /\
  Some? kt.parser_kind_high /\
  Some? k.parser_kind_high /\ (
  let (Some vt) = kt.parser_kind_high in
  let (Some v) = k.parser_kind_high in
  vt + v < 4294967296
  )

inline_for_extraction
let parse32_sum_t (t: sum) : Tot Type =
  bytes32 -> Tot (option (sum_type t * U32.t))

let parse32_sum_eq (t: sum) : Tot (parse32_sum_t t -> parse32_sum_t t -> GTot Type0) =
  feq _ _ (eq2 #_)

inline_for_extraction
let parse32_sum_if (t: sum) : Tot (if_combinator _ (parse32_sum_eq t)) =
  fif _ _ _ (default_if _)

let parse32_sum_eq_refl (t: sum) : Tot (r_reflexive_t _ (parse32_sum_eq t)) =
  fun _ -> ()

let parse32_sum_eq_trans (t: sum) : Tot (r_transitive_t _ (parse32_sum_eq t)) =
  fun _ _ _ -> ()

#set-options "--z3rlimit 32"

let parse32_sum_aux
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
: GTot (parser32 (parse_sum t p pc))
= fun input ->
  parse_sum_eq' t p pc (B32.reveal input);
  [@inline_let]
  let res : option (sum_type t * U32.t) =
    match p32 input with
    | None -> None
    | Some (k, consumed_k) ->
      begin
        let input_k = B32.b32slice input consumed_k (B32.len input) in
        synth_sum_case_injective t k;
        match
          parse32_synth'
            (dsnd (pc k))
            (synth_sum_case t k)
            (pc32 k)
            ()
            input_k
        with
        | None -> None
        | Some (x, consumed_x) -> Some ((x <: sum_type t), consumed_k `U32.add` consumed_x)
      end
  in
  (res <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } ))

inline_for_extraction
let parse32_sum'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
  (destr: enum_destr_t (option (sum_type t * U32.t)) (sum_enum t))
  (input: B32.bytes)
: Pure (option (sum_type t * U32.t))
  (requires True)
  (ensures (fun res -> res == parse32_sum_aux t p p32 pc pc32 input))
= [@inline_let]
  let res : option (sum_type t * U32.t) =
    match p32 input with
    | None -> None
    | Some (k, consumed_k) ->
      let input_k = B32.b32slice input consumed_k (B32.len input) in
      synth_sum_case_injective t k;
      [@inline_let]
      let f
        (k: sum_key t)
      : Tot (option (sum_type t * U32.t))
      = synth_sum_case_injective t k;
        parse32_synth'
          (dsnd (pc k))
          (synth_sum_case t k)
          (pc32 k)
          ()
          input_k
      in
      [@inline_let]
      let f_prop
        (k: sum_key t)
      : Lemma
        (match f k with
          | None -> True
          | Some (_, consumed_x) ->
            FStar.UInt.size (U32.v consumed_k + U32.v consumed_x) 32
        )
      = match f k with
        | None -> ()
        | Some (_, consumed_x) ->
          assert (U32.v consumed_k + U32.v consumed_x <= B32.length input)
      in
      [@inline_let]
      let j : option (sum_type t * U32.t) = destr (eq2 #(option (sum_type t * U32.t))) (default_if _) (fun _ -> ()) (fun _ _ _ -> ()) (fun k -> f k) k in
      [@inline_let]
      let _ : squash (j == f k) = assert (j == f k) in
      [@inline_let]
      let _ = f_prop k in
      begin match j with
      | None -> None
      | Some (x, consumed_x) ->
        Some (x, consumed_k `U32.add` consumed_x)
      end
  in
  res

#reset-options

inline_for_extraction
let parse32_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
  (destr: enum_destr_t (option (sum_type t * U32.t)) (sum_enum t))
: Tot (parser32 (parse_sum t p pc))
= fun input ->
  (parse32_sum' t p p32 pc pc32 destr input <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } ))


let serialize32_sum_aux
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (s32: serializer32 (serialize_enum_key _ s (sum_enum t)))
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: squash (serializer32_sum_gen_precond kt (weaken_parse_cases_kind t pc)))
: GTot (serializer32 (serialize_sum t s sc))
= fun x ->
  serialize_sum_eq t s sc x;
  let tg = sum_tag_of_data t x in
  let s1 = s32 tg in
  let s2 = sc32 tg (synth_sum_case_recip t tg x) in
  let res = s1 `B32.b32append` s2 in
  (res <: (res: B32.bytes { serializer32_correct (serialize_sum t s sc) x res } ))

inline_for_extraction
let serialize32_sum_destr_codom
  (t: sum)
  (k: sum_key t)
: Tot Type
= refine_with_tag (sum_tag_of_data t) k -> Tot B32.bytes

module T = FStar.Tactics

let serialize32_sum_destr_eq
  (t: sum)
  (k: sum_key t)
: Tot (serialize32_sum_destr_codom t k -> serialize32_sum_destr_codom t k -> GTot Type0)
= _ by (T.apply (`feq); T.apply (`eq2))

inline_for_extraction
let serialize32_sum_destr_if
  (t: sum)
  (k: sum_key t)
: Tot (if_combinator _ (serialize32_sum_destr_eq t k))
= // _ by (T.apply (`fif); T.fail "abc")
  fif _ _ _ (default_if _) 

#set-options "--z3rlimit 16"

inline_for_extraction
let serialize32_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (s32: serializer32 (serialize_enum_key _ s (sum_enum t)))
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (serialize32_sum_destr_codom t))
  (u: squash (serializer32_sum_gen_precond kt (weaken_parse_cases_kind t pc)))
: Tot (serializer32 (serialize_sum t s sc))
= fun x ->
  [@inline_let]
  let _ = serialize_sum_eq t s sc x in
  let tg = sum_tag_of_data t x in
  let s1 = s32 tg in
  let s2 = destr
    (serialize32_sum_destr_eq t)
    (serialize32_sum_destr_if t)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (fun tg x -> sc32 tg (synth_sum_case_recip t tg x))
    tg
    x
  in
  let res = s1 `B32.b32append` s2 in
  (res <: (res: B32.bytes { serializer32_correct (serialize_sum t s sc) x res } ))

#reset-options

inline_for_extraction
let size32_sum_destr_codom
  (t: sum)
  (k: sum_key t)
: Tot Type
= refine_with_tag (sum_tag_of_data t) k -> Tot U32.t

let size32_sum_destr_eq
  (t: sum)
  (k: sum_key t)
: Tot (size32_sum_destr_codom t k -> size32_sum_destr_codom t k -> GTot Type0)
= _ by (T.apply (`feq); T.apply (`eq2))

inline_for_extraction
let size32_sum_destr_if
  (t: sum)
  (k: sum_key t)
: Tot (if_combinator _ (size32_sum_destr_eq t k))
= // _ by (T.apply (`fif); T.fail "abc")
  fif _ _ _ (default_if _) 

let size32_sum_gen_precond
  (kt: parser_kind)
  (k: parser_kind)
: GTot Type0
= kt.parser_kind_subkind == Some ParserStrong /\
  Some? kt.parser_kind_high /\
  Some? k.parser_kind_high /\ (
  let (Some vt) = kt.parser_kind_high in
  let (Some v) = k.parser_kind_high in
  vt + v < 4294967295
  )

#set-options "--z3rlimit 16"

inline_for_extraction
let size32_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (s32: size32 (serialize_enum_key _ s (sum_enum t)))
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (size32 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (size32_sum_destr_codom t))
  (u: squash (size32_sum_gen_precond kt (weaken_parse_cases_kind t pc)))
: Tot (size32 (serialize_sum t s sc))
= fun x ->
  serialize_sum_eq t s sc x;
  let tg = sum_tag_of_data t x in
  let s1 = s32 tg in
  let s2 = destr
    (size32_sum_destr_eq t)
    (size32_sum_destr_if t)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (fun tg x -> sc32 tg (synth_sum_case_recip t tg x))
    tg
    x
  in
  assert_norm (U32.v u32_max == 4294967295);
  let res = s1 `U32.add` s2 in
  (res <: (res: U32.t { size32_postcond (serialize_sum t s sc) x res } ))

#reset-options

(* Sum with default case *)

#set-options "--z3rlimit 32"

let parse32_dsum_aux
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (p32: parser32 p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (parser32 (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: parser32 g)
: GTot (parser32 (parse_dsum t p f g))
= fun input ->
  parse_dsum_eq' t p f g (B32.reveal input);
  let res : option (dsum_type t * U32.t) =
    match p32 input with
    | None -> None
    | Some (k', consumed_k) ->
      let k = maybe_enum_key_of_repr (dsum_enum t) k' in
      let input_k = B32.b32slice input consumed_k (B32.len input) in
      synth_dsum_case_injective t k;
      begin match k with
      | Known k_ ->
        begin
          match
            parse32_synth'
              (dsnd (f k_))
              (synth_dsum_case t k)
              (f32 k_)
              ()
              input_k
          with
          | None -> None
          | Some (x, consumed_x) ->
            assert (U32.v consumed_k + U32.v consumed_x <= B32.length input);
            Some ((x <: dsum_type t), consumed_k `U32.add` consumed_x)
        end
      | Unknown k_ ->
        synth_dsum_case_injective t k;
        begin
          match
            parse32_synth'
              g
              (synth_dsum_case t k)
              g32
              ()
              input_k
          with
          | None -> None
          | Some (x, consumed_x) ->
            assert (U32.v consumed_k + U32.v consumed_x <= B32.length input);
            Some ((x <: dsum_type t), consumed_k `U32.add` consumed_x)
        end
      end
  in
  (res <: (res: option (dsum_type t * U32.t) { parser32_correct (parse_dsum t p f g) input res } ))

inline_for_extraction
let parse32_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (p32: parser32 p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (parser32 (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: parser32 g)
  (destr: maybe_enum_destr_t (option (dsum_type t * U32.t)) (dsum_enum t))
  (input: B32.bytes)
: Pure (option (dsum_type t * U32.t))
  (requires True)
  (ensures (fun res -> res == parse32_dsum_aux t p32 f f32 g32 input))
= match p32 input with
  | None -> None
  | Some (k', consumed_k) ->
    let input_k = B32.b32slice input consumed_k (B32.len input) in
    [@inline_let]
    let f (k: maybe_enum_key (dsum_enum t)) : Tot (option (dsum_type t * U32.t)) =
      [@inline_let]
      let _ = synth_dsum_case_injective t k in
      begin match k with
      | Known k_ ->
        begin
          match
            parse32_synth'
              (dsnd (f k_))
              (synth_dsum_case t k)
              (f32 k_)
              ()
              input_k
          with
          | None -> None
          | Some (x, consumed_x) ->
            [@inline_let]
            let _ = assert (U32.v consumed_k + U32.v consumed_x <= B32.length input) in
            Some ((x <: dsum_type t), consumed_k `U32.add` consumed_x)
        end
      | Unknown k_ ->
        begin
          match
            parse32_synth'
              g
              (synth_dsum_case t k)
              g32
              ()
              input_k
          with
          | None -> None
          | Some (x, consumed_x) ->
            [@inline_let]
            let _ = assert (U32.v consumed_k + U32.v consumed_x <= B32.length input) in
            Some ((x <: dsum_type t), consumed_k `U32.add` consumed_x)
        end
      end
    in
    destr (eq2 #_) (default_if _) (fun _ -> ()) (fun _ _ _ -> ()) f k'

#reset-options

inline_for_extraction
let parse32_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (p32: parser32 p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (parser32 (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: parser32 g)
  (destr: maybe_enum_destr_t (option (dsum_type t * U32.t)) (dsum_enum t))
: Tot (parser32 (parse_dsum t p f g))
= fun input ->
  (parse32_dsum' t p32 f f32 g32 destr input <: (res: option (dsum_type t * U32.t) { parser32_correct (parse_dsum t p f g) input res } ))

inline_for_extraction
let serialize32_dsum_type_of_tag
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (tg: dsum_key t)
: Tot (serializer32 (serialize_dsum_type_of_tag t f sf g sg tg))
= match tg with
  | Known x' -> serialize32_ext (dsnd (f x')) (sf x') (sf32 x') (parse_dsum_type_of_tag t f g tg) ()
  | Unknown x' -> serialize32_ext g sg sg32 (parse_dsum_type_of_tag t f g tg) ()

inline_for_extraction
let serialize32_dsum_cases
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (tg: dsum_key t)
: Tot (serializer32 (serialize_dsum_cases t f sf g sg tg))
= [@inline_let]
  let _ = synth_dsum_case_injective t tg in
  [@inline_let]
  let _ = synth_dsum_case_inverse t tg in
  serialize32_synth' _ (synth_dsum_case t tg) _ (serialize32_dsum_type_of_tag t f sf sf32 sg32 tg) (synth_dsum_case_recip t tg) ()

inline_for_extraction
let serialize32_dsum_known_destr_codom
  (t: dsum)
  (k: dsum_known_key t)
: Tot Type
= refine_with_tag (dsum_tag_of_data t) (Known k) -> Tot B32.bytes

let serialize32_dsum_known_destr_eq
  (t: dsum)
  (k: dsum_known_key t)
: Tot (serialize32_dsum_known_destr_codom t k -> serialize32_dsum_known_destr_codom t k -> GTot Type0)
= _ by (T.apply (`feq); T.apply (`eq2))

inline_for_extraction
let serialize32_dsum_known_destr_if
  (t: dsum)
  (k: dsum_known_key t)
: Tot (if_combinator _ (serialize32_dsum_known_destr_eq t k))
= fif _ _ _ (default_if _)

#set-options "--z3rlimit 32"

inline_for_extraction
let serialize32_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (s32: serializer32 (serialize_maybe_enum_key _ s (dsum_enum t)))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (destr: dep_enum_destr (dsum_enum t) (serialize32_dsum_known_destr_codom t))
  (u: squash (serializer32_sum_gen_precond kt (weaken_parse_dsum_cases_kind t f k')))
: Tot (serializer32 (serialize_dsum t s f sf g sg))
= fun x ->
  [@inline_let]
  let _ = serialize_dsum_eq' t s f sf g sg x in
  let tg = dsum_tag_of_data t x in
  let s1 = s32 tg in
  let s2 = match tg with
    | Known tg' -> destr (serialize32_dsum_known_destr_eq t) (serialize32_dsum_known_destr_if t) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (fun tg_ -> serialize32_dsum_cases t f sf sf32 sg32 (Known tg_)) tg' x
    | Unknown tg' -> serialize32_dsum_cases t f sf sf32 sg32 (Unknown tg') x
  in
  [@inline_let]
  let _ = assert (s2 == (serialize32_dsum_cases t f sf sf32 sg32 tg x)) in
  [@inline_let]
  let _ = assert (B32.length s1 + B32.length s2 < 4294967296) in
  let res = s1 `B32.b32append` s2 in
  [@inline_let]
  let _ = assert (serializer32_correct (serialize_dsum t s f sf g sg) x res) in
  (res <: (res: B32.bytes { serializer32_correct (serialize_dsum t s f sf g sg) x res } ))

#reset-options

inline_for_extraction
let size32_dsum_type_of_tag
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (size32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: size32 sg)
  (tg: dsum_key t)
: Tot (size32 (serialize_dsum_type_of_tag t f sf g sg tg))
= match tg with
  | Known x' -> size32_ext (dsnd (f x')) (sf x') (sf32 x') (parse_dsum_type_of_tag t f g tg) ()
  | Unknown x' -> size32_ext g sg sg32 (parse_dsum_type_of_tag t f g tg) ()

inline_for_extraction
let size32_dsum_cases
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (size32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: size32 sg)
  (tg: dsum_key t)
: Tot (size32 (serialize_dsum_cases t f sf g sg tg))
= [@inline_let]
  let _ = synth_dsum_case_injective t tg in
  [@inline_let]
  let _ = synth_dsum_case_inverse t tg in
  size32_synth' _ (synth_dsum_case t tg) _ (size32_dsum_type_of_tag t f sf sf32 sg32 tg) (synth_dsum_case_recip t tg) ()

inline_for_extraction
let size32_dsum_known_destr_codom
  (t: dsum)
  (k: dsum_known_key t)
: Tot Type
= refine_with_tag (dsum_tag_of_data t) (Known k) -> Tot U32.t

let size32_dsum_known_destr_eq
  (t: dsum)
  (k: dsum_known_key t)
: Tot (size32_dsum_known_destr_codom t k -> size32_dsum_known_destr_codom t k -> GTot Type0)
= _ by (T.apply (`feq); T.apply (`eq2))

inline_for_extraction
let size32_dsum_known_destr_if
  (t: dsum)
  (k: dsum_known_key t)
: Tot (if_combinator _ (size32_dsum_known_destr_eq t k))
= fif _ _ _ (default_if _)

#set-options "--z3rlimit 32"

inline_for_extraction
let size32_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (s32: size32 (serialize_maybe_enum_key _ s (dsum_enum t)))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (size32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: size32 sg)
  (destr: dep_enum_destr (dsum_enum t) (size32_dsum_known_destr_codom t))
  (u: squash (size32_sum_gen_precond kt (weaken_parse_dsum_cases_kind t f k')))
: Tot (size32 (serialize_dsum t s f sf g sg))
= fun x ->
  [@inline_let]
  let _ = serialize_dsum_eq' t s f sf g sg x in
  let tg = dsum_tag_of_data t x in
  let s1 = s32 tg in
  let s2 = match tg with
    | Known tg' -> destr (size32_dsum_known_destr_eq t) (size32_dsum_known_destr_if t) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (fun tg_ -> size32_dsum_cases t f sf sf32 sg32 (Known tg_)) tg' x
    | Unknown tg' -> size32_dsum_cases t f sf sf32 sg32 (Unknown tg') x
  in
  [@inline_let]
  let _ = assert_norm (U32.v u32_max == 4294967295) in
  [@inline_let]
  let _ = assert (s2 == (size32_dsum_cases t f sf sf32 sg32 tg x)) in
  [@inline_let]
  let _ = assert (U32.v s1 + U32.v s2 < 4294967295) in
  let res = s1 `U32.add` s2 in
  [@inline_let]
  let _ = assert (size32_postcond (serialize_dsum t s f sf g sg) x res) in
  (res <: (res: U32.t { size32_postcond (serialize_dsum t s f sf g sg) x res } ))

#reset-options
